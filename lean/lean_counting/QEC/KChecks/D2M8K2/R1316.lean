import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5264 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5264 = true := by
  decide +kernel

theorem tot5264 : totK PD2M8K2 D2M8K2.t5264 = [0, 0, 163126407446, 449602270321, 278059225097, 30209020093, 0, 0] := by
  decide +kernel

theorem rows5265 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5265 = true := by
  decide +kernel

theorem tot5265 : totK PD2M8K2 D2M8K2.t5265 = [0, 0, 146713155126, 456969276739, 278867380598, 15489181051, 0, 0] := by
  decide +kernel

theorem rows5266 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5266 = true := by
  decide +kernel

theorem tot5266 : totK PD2M8K2 D2M8K2.t5266 = [0, 0, 0, 265885324608, 498811688454, 133635547331, 4031931762, 0] := by
  decide +kernel

theorem rows5267 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5267 = true := by
  decide +kernel

theorem tot5267 : totK PD2M8K2 D2M8K2.t5267 = [0, 0, 121689987511, 353839943909, 360009535274, 83961394553, 1186940923, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
