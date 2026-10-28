import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows14700 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14700 = true := by
  decide +kernel

theorem tot14700 : totK PD2M8K2 D2M8K2.t14700 = [0, 0, 207903899478, 472936980585, 173088921341, 9541089458, 0, 0] := by
  decide +kernel

theorem rows14701 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14701 = true := by
  decide +kernel

theorem tot14701 : totK PD2M8K2 D2M8K2.t14701 = [0, 0, 74650056613, 373926289740, 325683371412, 52787941742, 1138244013, 0] := by
  decide +kernel

theorem rows14702 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14702 = true := by
  decide +kernel

theorem tot14702 : totK PD2M8K2 D2M8K2.t14702 = [0, 0, 91324294812, 413356242521, 334827743624, 23652145588, 0, 0] := by
  decide +kernel

theorem rows14703 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14703 = true := by
  decide +kernel

theorem tot14703 : totK PD2M8K2 D2M8K2.t14703 = [0, 0, 205317498136, 462633079849, 226553342159, 14942475072, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
