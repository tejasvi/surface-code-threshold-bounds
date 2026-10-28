import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6936 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6936 = true := by
  decide +kernel

theorem tot6936 : totK PA10K2 A10K2.t6936 = [0, 0, 327737319032, 1568953172484, 2197696280233, 841828968419, 49237757113, 0, 0, 0] := by
  decide +kernel

theorem rows6937 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6937 = true := by
  decide +kernel

theorem tot6937 : totK PA10K2 A10K2.t6937 = [0, 0, 0, 591213232857, 2021733856922, 1926261141142, 423982282231, 13231026584, 0, 0] := by
  decide +kernel

theorem rows6938 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6938 = true := by
  decide +kernel

theorem tot6938 : totK PA10K2 A10K2.t6938 = [0, 320479959089, 824792189705, 741906840384, 1143575783822, 1372821376216, 529680438566, 49137536365, 0, 0] := by
  decide +kernel

theorem rows6939 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6939 = true := by
  decide +kernel

theorem tot6939 : totK PA10K2 A10K2.t6939 = [0, 445226740873, 1723804370075, 1926381277215, 569009116308, 32846095359, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
