import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5272 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5272 = true := by
  decide +kernel

theorem tot5272 : totK PD2M8K2 D2M8K2.t5272 = [0, 0, 122989245013, 462560489342, 304572406022, 21568850423, 0, 0] := by
  decide +kernel

theorem rows5273 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5273 = true := by
  decide +kernel

theorem tot5273 : totK PD2M8K2 D2M8K2.t5273 = [0, 0, 0, 236707115848, 508583402285, 142115936031, 1238673482, 0] := by
  decide +kernel

theorem rows5274 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5274 = true := by
  decide +kernel

theorem tot5274 : totK PD2M8K2 D2M8K2.t5274 = [0, 87633958636, 222239884900, 173701574083, 256372471264, 125335128258, 8063697217, 0] := by
  decide +kernel

theorem rows5275 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5275 = true := by
  decide +kernel

theorem tot5275 : totK PD2M8K2 D2M8K2.t5275 = [0, 200918460017, 476208154130, 209186399507, 12781111781, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
