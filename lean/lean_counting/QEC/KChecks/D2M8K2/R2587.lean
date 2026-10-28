import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows10348 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10348 = true := by
  decide +kernel

theorem tot10348 : totK PD2M8K2 D2M8K2.t10348 = [0, 106226520538, 354739680563, 347255989495, 90285825006, 3579068459, 0, 0] := by
  decide +kernel

theorem rows10349 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10349 = true := by
  decide +kernel

theorem tot10349 : totK PD2M8K2 D2M8K2.t10349 = [0, 170647192212, 444183425118, 268010560602, 27991424991, 0, 0, 0] := by
  decide +kernel

theorem rows10350 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10350 = true := by
  decide +kernel

theorem tot10350 : totK PD2M8K2 D2M8K2.t10350 = [0, 164986643072, 460534943147, 277894829258, 22069572119, 0, 0, 0] := by
  decide +kernel

theorem rows10351 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10351 = true := by
  decide +kernel

theorem tot10351 : totK PD2M8K2 D2M8K2.t10351 = [0, 0, 239214450480, 507807344303, 143322647893, 2304167554, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
