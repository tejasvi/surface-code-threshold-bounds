import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows15996 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15996 = true := by
  decide +kernel

theorem tot15996 : totK PD2M8K2 D2M8K2.t15996 = [0, 0, 211630803855, 471493155669, 187642849845, 9786135328, 0, 0] := by
  decide +kernel

theorem rows15997 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15997 = true := by
  decide +kernel

theorem tot15997 : totK PD2M8K2 D2M8K2.t15997 = [0, 0, 86353460783, 393838006404, 353730260739, 44977450277, 0, 0] := by
  decide +kernel

theorem rows15998 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15998 = true := by
  decide +kernel

theorem tot15998 : totK PD2M8K2 D2M8K2.t15998 = [0, 0, 0, 296146247850, 498429366268, 78667357707, 0, 0] := by
  decide +kernel

theorem rows15999 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15999 = true := by
  decide +kernel

theorem tot15999 : totK PD2M8K2 D2M8K2.t15999 = [0, 0, 193349602110, 448363396366, 269558975576, 31381895006, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
