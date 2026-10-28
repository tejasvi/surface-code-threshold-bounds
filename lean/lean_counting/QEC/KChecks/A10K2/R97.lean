import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows388 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t388 = true := by
  decide +kernel

theorem tot388 : totK PA10K2 A10K2.t388 = [0, 0, 479394299813, 1869496333134, 2031030678016, 527393498139, 25462924663, 0, 0, 0] := by
  decide +kernel

theorem rows389 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t389 = true := by
  decide +kernel

theorem tot389 : totK PA10K2 A10K2.t389 = [0, 0, 0, 724349211821, 2181159624372, 1630366790456, 279497564286, 6904928264, 0, 0] := by
  decide +kernel

theorem rows390 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t390 = true := by
  decide +kernel

theorem tot390 : totK PA10K2 A10K2.t390 = [0, 0, 404116090896, 1646678666233, 2086813932605, 840438740182, 69102974393, 0, 0, 0] := by
  decide +kernel

theorem rows391 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t391 = true := by
  decide +kernel

theorem tot391 : totK PA10K2 A10K2.t391 = [0, 0, 222606760118, 1169447766106, 2082665635057, 1301405745560, 198271561525, 6766355402, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
