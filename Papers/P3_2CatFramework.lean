/-
  Papers/P3_2CatFramework.lean
  
  Main import file for Paper 3's 2-categorical framework.
  This brings together all the phases of the implementation.
-/

-- Phase 1: Basic bicategorical structure
import Papers.P3_2CatFramework.Phase1_Simple

-- Phase 2: Uniformization height theory
import Papers.P3_2CatFramework.Phase2_UniformHeight
import Papers.P3_2CatFramework.Phase2_API

-- Phase 3: Numeric levels and obstruction framework
import Papers.P3_2CatFramework.Phase3_Levels
import Papers.P3_2CatFramework.Phase3_Obstruction
import Papers.P3_2CatFramework.Phase3_StoneWindowMock

-- Positive uniformization (Part II of paper)
import Papers.P3_2CatFramework.Phase2_Positive
import Papers.P3_2CatFramework.Phase3_Positive