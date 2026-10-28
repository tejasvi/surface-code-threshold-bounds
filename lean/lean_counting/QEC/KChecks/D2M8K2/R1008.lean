import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4032 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4032 = true := by
  decide +kernel

theorem tot4032 : totK PD2M8K2 D2M8K2.t4032 = [0, 124243985619, 359254292665, 325930566307, 92065913103, 3632925411, 0, 0] := by
  decide +kernel

theorem rows4033 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4033 = true := by
  decide +kernel

theorem tot4033 : totK PD2M8K2 D2M8K2.t4033 = [0, 175268696151, 442525451233, 274779450758, 30191107111, 0, 0, 0] := by
  decide +kernel

theorem rows4034 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4034 = true := by
  decide +kernel

theorem tot4034 : totK PD2M8K2 D2M8K2.t4034 = [0, 125863117380, 440185302200, 318704056033, 25841327228, 0, 0, 0] := by
  decide +kernel

theorem rows4035 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4035 = true := by
  decide +kernel

theorem tot4035 : totK PD2M8K2 D2M8K2.t4035 = [0, 0, 226219587617, 494435587250, 167244556903, 3439610676, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
