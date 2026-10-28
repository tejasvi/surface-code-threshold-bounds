import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5408 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5408 = true := by
  decide +kernel

theorem tot5408 : totK PD2M8K2 D2M8K2.t5408 = [0, 0, 177164378844, 429500458366, 258448299696, 52276311856, 1429815836, 0] := by
  decide +kernel

theorem rows5409 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5409 = true := by
  decide +kernel

theorem tot5409 : totK PD2M8K2 D2M8K2.t5409 = [0, 0, 190368838091, 462920778237, 230248055784, 15429351258, 0, 0] := by
  decide +kernel

theorem rows5410 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5410 = true := by
  decide +kernel

theorem tot5410 : totK PD2M8K2 D2M8K2.t5410 = [0, 0, 56561114677, 344679719404, 430861796828, 79991158221, 0, 0] := by
  decide +kernel

theorem rows5411 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5411 = true := by
  decide +kernel

theorem tot5411 : totK PD2M8K2 D2M8K2.t5411 = [0, 0, 0, 209133099972, 478994185094, 178164717979, 4845320938, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
