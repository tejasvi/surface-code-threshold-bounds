import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows576 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t576 = true := by
  decide +kernel

theorem tot576 : totK PA10K2 A10K2.t576 = [0, 296845519927, 1541390001922, 2112575393926, 741380298358, 52620953014, 0, 0, 0, 0] := by
  decide +kernel

theorem rows577 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t577 = true := by
  decide +kernel

theorem tot577 : totK PA10K2 A10K2.t577 = [0, 110960779961, 802472415244, 2054747070108, 1467278359478, 248488922356, 6354482628, 0, 0, 0] := by
  decide +kernel

theorem rows578 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t578 = true := by
  decide +kernel

theorem tot578 : totK PA10K2 A10K2.t578 = [0, 270525779411, 1170554858192, 1949769269034, 1282148345858, 241217338574, 6962742351, 0, 0, 0] := by
  decide +kernel

theorem rows579 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t579 = true := by
  decide +kernel

theorem tot579 : totK PA10K2 A10K2.t579 = [0, 463622061231, 1868879014697, 1920773339623, 464000280055, 25686058060, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
