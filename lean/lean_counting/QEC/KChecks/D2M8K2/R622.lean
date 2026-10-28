import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2488 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2488 = true := by
  decide +kernel

theorem tot2488 : totK PD2M8K2 D2M8K2.t2488 = [52364295763, 333563265136, 424347551675, 90464885486, 1164319620, 0, 0, 0] := by
  decide +kernel

theorem rows2489 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2489 = true := by
  decide +kernel

theorem tot2489 : totK PD2M8K2 D2M8K2.t2489 = [0, 203961726709, 490658935294, 180487054510, 9404247146, 0, 0, 0] := by
  decide +kernel

theorem rows2490 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2490 = true := by
  decide +kernel

theorem tot2490 : totK PD2M8K2 D2M8K2.t2490 = [163678763449, 440304841107, 260747472197, 39264116820, 1503593968, 0, 0, 0] := by
  decide +kernel

theorem rows2491 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2491 = true := by
  decide +kernel

theorem tot2491 : totK PD2M8K2 D2M8K2.t2491 = [156078620184, 438486469622, 284148677272, 26079896842, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
