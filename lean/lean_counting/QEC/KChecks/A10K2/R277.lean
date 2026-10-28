import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1108 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1108 = true := by
  decide +kernel

theorem tot1108 : totK PA10K2 A10K2.t1108 = [0, 0, 0, 533646324746, 2008260151219, 2115110228120, 448328928390, 13229391832, 0, 0] := by
  decide +kernel

theorem rows1109 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1109 = true := by
  decide +kernel

theorem tot1109 : totK PA10K2 A10K2.t1109 = [0, 0, 0, 398069475251, 1557860674917, 2051710196745, 792354523120, 61619070123, 0, 0] := by
  decide +kernel

theorem rows1110 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1110 = true := by
  decide +kernel

theorem tot1110 : totK PA10K2 A10K2.t1110 = [0, 0, 0, 403409144169, 1798178676777, 2053161461546, 640880690137, 41536843173, 0, 0] := by
  decide +kernel

theorem rows1111 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1111 = true := by
  decide +kernel

theorem tot1111 : totK PA10K2 A10K2.t1111 = [0, 0, 0, 197157298755, 1138565877567, 2025810720424, 1202242473125, 189443954979, 6725424603, 0] := by
  decide +kernel

end QECKChecks.A10K2
