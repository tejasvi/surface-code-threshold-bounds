import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows10536 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10536 = true := by
  decide +kernel

theorem tot10536 : totK PD2M8K2 D2M8K2.t10536 = [0, 170040538896, 483093788469, 236286619236, 12346377983, 0, 0, 0] := by
  decide +kernel

theorem rows10537 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10537 = true := by
  decide +kernel

theorem tot10537 : totK PD2M8K2 D2M8K2.t10537 = [0, 0, 269999631630, 492158433864, 133847904729, 6972471598, 0, 0] := by
  decide +kernel

theorem rows10538 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10538 = true := by
  decide +kernel

theorem tot10538 : totK PD2M8K2 D2M8K2.t10538 = [0, 67638813973, 316540279634, 394762303298, 104249117339, 4900554076, 0, 0] := by
  decide +kernel

theorem rows10539 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10539 = true := by
  decide +kernel

theorem tot10539 : totK PD2M8K2 D2M8K2.t10539 = [0, 181846759548, 454395788565, 269832644115, 28083780415, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
