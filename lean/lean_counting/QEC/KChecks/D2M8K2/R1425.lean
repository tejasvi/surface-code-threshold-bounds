import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5700 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5700 = true := by
  decide +kernel

theorem tot5700 : totK PD2M8K2 D2M8K2.t5700 = [0, 0, 166673281812, 466227703780, 209314153357, 13266036910, 0, 0] := by
  decide +kernel

theorem rows5701 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5701 = true := by
  decide +kernel

theorem tot5701 : totK PD2M8K2 D2M8K2.t5701 = [0, 0, 234884802847, 481791951843, 154399299471, 7791373183, 0, 0] := by
  decide +kernel

theorem rows5702 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5702 = true := by
  decide +kernel

theorem tot5702 : totK PD2M8K2 D2M8K2.t5702 = [0, 0, 172507831794, 455644674509, 206111532491, 17711536120, 0, 0] := by
  decide +kernel

theorem rows5703 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5703 = true := by
  decide +kernel

theorem tot5703 : totK PD2M8K2 D2M8K2.t5703 = [0, 0, 237866319323, 499336628793, 153523374645, 4140638705, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
