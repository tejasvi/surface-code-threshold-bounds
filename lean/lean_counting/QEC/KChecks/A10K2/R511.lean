import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2044 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2044 = true := by
  decide +kernel

theorem tot2044 : totK PA10K2 A10K2.t2044 = [0, 157431001564, 870774013470, 2004954446855, 1353839825692, 207609599557, 6121173289, 0, 0, 0] := by
  decide +kernel

theorem rows2045 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2045 = true := by
  decide +kernel

theorem tot2045 : totK PA10K2 A10K2.t2045 = [0, 505943982414, 1909391651978, 2019505751535, 558611273976, 31429059140, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2046 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2046 = true := by
  decide +kernel

theorem tot2046 : totK PA10K2 A10K2.t2046 = [318927245577, 1005840620052, 1496123267870, 1364053440235, 549229200616, 50311706348, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2047 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2047 = true := by
  decide +kernel

theorem tot2047 : totK PA10K2 A10K2.t2047 = [105428430234, 1059606708021, 1928618052815, 1106325777894, 283186490347, 25371180993, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
