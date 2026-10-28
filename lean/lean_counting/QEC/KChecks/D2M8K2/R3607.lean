import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows14428 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14428 = true := by
  decide +kernel

theorem tot14428 : totK PD2M8K2 D2M8K2.t14428 = [37073650097, 347704874170, 466383481305, 60435619413, 0, 0, 0, 0] := by
  decide +kernel

theorem rows14429 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14429 = true := by
  decide +kernel

theorem tot14429 : totK PD2M8K2 D2M8K2.t14429 = [199649395821, 473190219339, 206055832883, 9847636232, 0, 0, 0, 0] := by
  decide +kernel

theorem rows14430 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14430 = true := by
  decide +kernel

theorem tot14430 : totK PD2M8K2 D2M8K2.t14430 = [84757123505, 380807386833, 364887736449, 63023523844, 1164319620, 0, 0, 0] := by
  decide +kernel

theorem rows14431 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14431 = true := by
  decide +kernel

theorem tot14431 : totK PD2M8K2 D2M8K2.t14431 = [0, 184387008138, 467459325325, 192776628243, 11885407614, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
