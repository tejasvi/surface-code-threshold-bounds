import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6252 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6252 = true := by
  decide +kernel

theorem tot6252 : totK PA10K2 A10K2.t6252 = [0, 113839911969, 484999313731, 1481052801888, 2074634089001, 843154188751, 63233022410, 0, 0, 0] := by
  decide +kernel

theorem rows6253 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6253 = true := by
  decide +kernel

theorem tot6253 : totK PA10K2 A10K2.t6253 = [0, 479358574261, 1836054687232, 1937096673320, 519888615253, 31485692778, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6254 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6254 = true := by
  decide +kernel

theorem tot6254 : totK PA10K2 A10K2.t6254 = [0, 184626183377, 1135593759999, 2094613927558, 1292813001486, 250283751399, 20029934272, 0, 0, 0] := by
  decide +kernel

theorem rows6255 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6255 = true := by
  decide +kernel

theorem tot6255 : totK PA10K2 A10K2.t6255 = [0, 252837937403, 1054524775708, 1899054873096, 1393647952117, 259191826491, 5265465927, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
