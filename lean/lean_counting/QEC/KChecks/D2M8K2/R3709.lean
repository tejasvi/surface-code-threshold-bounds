import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows14836 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14836 = true := by
  decide +kernel

theorem tot14836 : totK PD2M8K2 D2M8K2.t14836 = [0, 164815069247, 459334018937, 268930771222, 16745570091, 0, 0, 0] := by
  decide +kernel

theorem rows14837 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14837 = true := by
  decide +kernel

theorem tot14837 : totK PD2M8K2 D2M8K2.t14837 = [103793967717, 324754977307, 320340256714, 143846737252, 13566920432, 0, 0, 0] := by
  decide +kernel

theorem rows14838 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14838 = true := by
  decide +kernel

theorem tot14838 : totK PD2M8K2 D2M8K2.t14838 = [188798175226, 458016491928, 225377973052, 16924940264, 0, 0, 0, 0] := by
  decide +kernel

theorem rows14839 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14839 = true := by
  decide +kernel

theorem tot14839 : totK PD2M8K2 D2M8K2.t14839 = [107005299722, 420080131882, 323164802224, 31236747685, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
