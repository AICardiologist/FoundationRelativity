# Recovery Commands for Sprint 35 Session Restart

**Purpose**: Exact commands to restore working state and continue Sprint 35  
**Context**: Shell session broken, CI failing, need systematic recovery  

---

## 🔄 **IMMEDIATE RECOVERY COMMANDS**

### **1. Check Current Status**
```bash
# Verify current branch and commit
git status
git log --oneline -n 5

# Expected: On feat/cheeger-bottleneck, commit ae99d1c (failing) or 0690689 (working)
```

### **2. Restore Last Working State (Day 5)**
```bash
# If currently on failing commit, rollback to Day 5 working state
git reset --hard 0690689

# Verify rollback successful
git log --oneline -n 3
# Should show: 0690689 feat(cheeger): finish bridge theorem, file now sorry‑free (Day 5)

# Check that file is sorry-free
grep -n "sorry" SpectralGap/Cheeger.lean
# Should return: no matches (0 sorry statements)
```

### **3. Verify Working State**
```bash
# Test build from clean state
lake clean
lake build SpectralGap.Cheeger

# Should complete successfully without errors
# Build time should be < 60s
```

### **4. Create Recovery Branch (Optional)**
```bash
# Create backup branch at working state
git checkout -b feat/cheeger-day5-working
git push --set-upstream origin feat/cheeger-day5-working

# Return to main feature branch
git checkout feat/cheeger-bottleneck
```

---

## 🔍 **MATHLIB API RESEARCH**

### **Research Required APIs**
```bash
# Check mathlib version
cat lake-manifest.json | grep -A5 -B5 mathlib

# Search for diagonal operator APIs
find .lake/packages/mathlib -name "*.lean" -exec grep -l "diagonal.*self" {} \;
find .lake/packages/mathlib -name "*.lean" -exec grep -l "diagonal.*norm" {} \;

# Look for existing examples
grep -r "ContinuousLinearMap.diagonal" .lake/packages/mathlib/ | head -10
```

### **Alternative API Discovery**
```bash
# Use lean to explore available APIs
echo 'import Mathlib.Analysis.NormedSpace.OperatorNorm.Basic
#check ContinuousLinearMap.isSelfAdjoint' | lake env lean --stdin

echo 'import Mathlib.Analysis.NormedSpace.OperatorNorm.Basic  
#check ContinuousLinearMap.opNorm' | lake env lean --stdin
```

---

## 🛠️ **SYSTEMATIC DAY 6 RE-APPLICATION**

### **Step 1: Apply Documentation Only**
```bash
# Start from working Day 5 state
git reset --hard 0690689

# Create docs file (safe change)
mkdir -p docs
# Then add the cheeger-pathology.md content manually

# Test that this doesn't break build
lake build
```

### **Step 2: Update SpectralGap/Proofs.lean**
```bash
# Add ONLY the import and re-export, test immediately
# Edit SpectralGap/Proofs.lean to add:
# import SpectralGap.Cheeger
# theorem Cheeger_requires_ACω' (hsel : Sel) :
#     RequiresACω ∧ witness_cheeger :=
#   Cheeger_requires_ACω hsel

# Test build after each change
lake build SpectralGap.Proofs
```

### **Step 3: Test API Changes Incrementally**
```bash
# DO NOT CHANGE SpectralGap/Cheeger.lean until APIs are verified
# Research working APIs first

# Test any API changes in isolation:
# 1. Copy SpectralGap/Cheeger.lean to backup
# 2. Make minimal change
# 3. Test build immediately
# 4. Rollback if fails, research alternative
```

---

## 🎯 **DAY 7 PREPARATION**

### **Once CI is Green**
```bash
# Commit working Day 6 changes
git add docs/cheeger-pathology.md SpectralGap/Proofs.lean
git commit -m "docs(cheeger): add pathology doc and public API export (Day 6)

- Add complete pathology reference documentation
- Export Cheeger_requires_ACω via SpectralGap/Proofs.lean  
- Ready for Day 7 PR finalization"

git push origin feat/cheeger-bottleneck
```

### **PR Status Update**
```bash
# Verify PR shows green CI
# Expected status:
# - All builds passing
# - Runtime < 70s  
# - 0 sorry statements
# - Documentation complete
```

### **Ready for Math-AI Day 7**
```bash
# Confirm ready for final patch:
echo "Ready for Day 7 Math-AI patch: CHANGELOG + PR ready-for-review"
```

---

## 🚨 **EMERGENCY COMMANDS**

### **If Build Completely Broken**
```bash
# Nuclear option - start from main and cherry-pick working commits
git checkout main
git pull origin main
git checkout -b feat/cheeger-recovery

# Cherry-pick only the working Day 5 commit
git cherry-pick 0690689

# Test build
lake build

# If successful, make this the new working branch
git branch -D feat/cheeger-bottleneck
git checkout -b feat/cheeger-bottleneck
git push --force-with-lease origin feat/cheeger-bottleneck
```

### **If API Research Fails**
```bash
# Fall back to manual proof approach
# Replace API calls with sorry statements temporarily
# Commit as "wip: API compatibility layer needed"
# Continue with Day 7 to complete sprint
# Schedule API fixes for separate issue
```

---

## 📋 **VERIFICATION CHECKLIST**

### **Before Continuing**
- [ ] Git status shows clean working tree
- [ ] On feat/cheeger-bottleneck branch  
- [ ] SpectralGap/Cheeger.lean has 0 sorry statements
- [ ] `lake build` passes without errors
- [ ] Build time < 70 seconds
- [ ] CI status green (if push attempted)

### **After Any Changes**
- [ ] `lake build SpectralGap.Cheeger` passes
- [ ] `grep -n "sorry" SpectralGap/Cheeger.lean` returns 0 results
- [ ] `scripts/check-no-axioms.sh` passes
- [ ] File retains mathematical completeness from Day 5

### **Ready for Handoff**
- [ ] All documentation created
- [ ] API issues resolved or documented
- [ ] CI green and stable
- [ ] Math-AI can proceed with Day 7

---

## 🎯 **SUCCESS TARGETS**

### **Minimum Viable Recovery**
- Restore Day 5 working state (0 sorry, CI green)
- Add documentation files without breaking build
- Ready for Math-AI Day 7 patch

### **Optimal Recovery**  
- All Day 6 changes applied successfully
- APIs fixed for mathlib 4.22.0-rc3 compatibility
- Full CI green, ready for immediate Day 7

### **Fallback Position**
- Day 5 working state + documentation
- API issues documented for future resolution
- Sprint 35 mathematical goals achieved

---

**Recovery Priority**: URGENT  
**Timeline**: Complete before Math-AI Day 7 patch  
**Critical Path**: CI green + documentation complete  

---

*Recovery Commands - Sprint 35 Session Restart*