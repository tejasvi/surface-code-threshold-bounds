import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6428 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6428 = true := by
  decide +kernel

theorem tot6428 : totK PA10K2 A10K2.t6428 = [0, 539114903208, 1988368529070, 2018149685308, 473244498644, 13816090359, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6429 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6429 = true := by
  decide +kernel

theorem tot6429 : totK PA10K2 A10K2.t6429 = [0, 552138177800, 1920460080660, 1932030573955, 606207680860, 49180423016, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6430 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6430 = true := by
  decide +kernel

theorem tot6430 : totK PA10K2 A10K2.t6430 = [0, 399586008223, 1707099046849, 2157927626299, 733685237378, 43410424298, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6431 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6431 = true := by
  decide +kernel

theorem tot6431 : totK PA10K2 A10K2.t6431 = [0, 47234247204, 752481048101, 2165860948784, 1698186987732, 308817416976, 6904928264, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
