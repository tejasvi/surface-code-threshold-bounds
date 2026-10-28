import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5648 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5648 = true := by
  decide +kernel

theorem tot5648 : totK PA10K2 A10K2.t5648 = [0, 282771899135, 1528616529489, 2150992393124, 730812715829, 52575686575, 0, 0, 0, 0] := by
  decide +kernel

theorem rows5649 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5649 = true := by
  decide +kernel

theorem tot5649 : totK PA10K2 A10K2.t5649 = [0, 116178972112, 656503115605, 1710477003624, 1713446797280, 449645401387, 30831673886, 0, 0, 0] := by
  decide +kernel

theorem rows5650 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5650 = true := by
  decide +kernel

theorem tot5650 : totK PA10K2 A10K2.t5650 = [0, 459991179454, 1824867206139, 1990684340807, 527076186654, 26491486257, 0, 0, 0, 0] := by
  decide +kernel

theorem rows5651 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5651 = true := by
  decide +kernel

theorem tot5651 : totK PA10K2 A10K2.t5651 = [0, 197161727086, 1026301289827, 1913674273510, 1433027281740, 330446614486, 20340910120, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
