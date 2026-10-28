import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows14160 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14160 = true := by
  decide +kernel

theorem tot14160 : totK PD2M8K2 D2M8K2.t14160 = [0, 195071196084, 473439539285, 186739197811, 11873025674, 0, 0, 0] := by
  decide +kernel

theorem rows14161 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14161 = true := by
  decide +kernel

theorem tot14161 : totK PD2M8K2 D2M8K2.t14161 = [177909920641, 443821670153, 283651487779, 35368190153, 0, 0, 0, 0] := by
  decide +kernel

theorem rows14162 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14162 = true := by
  decide +kernel

theorem tot14162 : totK PD2M8K2 D2M8K2.t14162 = [153907372348, 457083934949, 277649724876, 29292505516, 0, 0, 0, 0] := by
  decide +kernel

theorem rows14163 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14163 = true := by
  decide +kernel

theorem tot14163 : totK PD2M8K2 D2M8K2.t14163 = [0, 221123414142, 496135297362, 166723742869, 8344820176, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
