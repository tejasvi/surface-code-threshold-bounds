import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows856 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t856 = true := by
  decide +kernel

theorem tot856 : totK PA10K2 A10K2.t856 = [291093484992, 1239221419210, 1945333144955, 1122502780632, 199002033244, 6354482628, 0, 0, 0, 0] := by
  decide +kernel

theorem rows857 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t857 = true := by
  decide +kernel

theorem tot857 : totK PA10K2 A10K2.t857 = [537828726768, 1892734670956, 2035949509084, 603480463806, 41567772668, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem rows858 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t858 = true := by
  decide +kernel

theorem tot858 : totK PA10K2 A10K2.t858 = [0, 719030763380, 2207907434772, 1756714440114, 311802433350, 6853348008, 0, 0, 0, 0] := by
  decide +kernel

theorem rows859 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t859 = true := by
  decide +kernel

theorem tot859 : totK PA10K2 A10K2.t859 = [0, 482250465084, 1771016168618, 2107730880660, 738856970525, 56126419230, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
