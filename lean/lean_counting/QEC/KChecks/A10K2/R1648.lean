import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6592 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6592 = true := by
  decide +kernel

theorem tot6592 : totK PA10K2 A10K2.t6592 = [0, 0, 0, 519195554369, 1874349820708, 1755393973731, 431997290024, 31003444686, 0, 0] := by
  decide +kernel

theorem rows6593 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6593 = true := by
  decide +kernel

theorem tot6593 : totK PA10K2 A10K2.t6593 = [0, 0, 513073702450, 1750387694593, 1843773643787, 579114848854, 47178914147, 0, 0, 0] := by
  decide +kernel

theorem rows6594 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6594 = true := by
  decide +kernel

theorem tot6594 : totK PA10K2 A10K2.t6594 = [0, 0, 306139930691, 1542522844416, 2060319266912, 696445040942, 52820011968, 0, 0, 0] := by
  decide +kernel

theorem rows6595 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6595 = true := by
  decide +kernel

theorem tot6595 : totK PA10K2 A10K2.t6595 = [0, 0, 0, 720399167104, 2170230304623, 1484784843540, 247766830408, 6354482628, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
