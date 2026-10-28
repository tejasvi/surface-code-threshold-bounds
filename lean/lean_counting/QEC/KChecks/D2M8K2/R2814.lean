import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows11256 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11256 = true := by
  decide +kernel

theorem tot11256 : totK PD2M8K2 D2M8K2.t11256 = [68713344269, 332247358887, 403213961053, 92350962220, 1369150432, 0, 0, 0] := by
  decide +kernel

theorem rows11257 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11257 = true := by
  decide +kernel

theorem tot11257 : totK PD2M8K2 D2M8K2.t11257 = [93572267332, 374784994756, 394949655873, 56992415291, 0, 0, 0, 0] := by
  decide +kernel

theorem rows11258 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11258 = true := by
  decide +kernel

theorem tot11258 : totK PD2M8K2 D2M8K2.t11258 = [162239846370, 448545274631, 283006526776, 22744083141, 0, 0, 0, 0] := by
  decide +kernel

theorem rows11259 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11259 = true := by
  decide +kernel

theorem tot11259 : totK PD2M8K2 D2M8K2.t11259 = [173103278718, 461387213909, 244298259240, 15329165425, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
