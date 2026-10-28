import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7408 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7408 = true := by
  decide +kernel

theorem tot7408 : totK PD2M8K2 D2M8K2.t7408 = [0, 169054490967, 468973191369, 235259799318, 12217687729, 0, 0, 0] := by
  decide +kernel

theorem rows7409 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7409 = true := by
  decide +kernel

theorem tot7409 : totK PD2M8K2 D2M8K2.t7409 = [0, 69375867204, 348533077720, 387089054280, 80897902769, 1369150432, 0, 0] := by
  decide +kernel

theorem rows7410 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7410 = true := by
  decide +kernel

theorem tot7410 : totK PD2M8K2 D2M8K2.t7410 = [0, 93537328149, 384064833176, 393632429488, 51371191069, 0, 0, 0] := by
  decide +kernel

theorem rows7411 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7411 = true := by
  decide +kernel

theorem tot7411 : totK PD2M8K2 D2M8K2.t7411 = [0, 172972077598, 452235485939, 256191249811, 19111649463, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
