import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2856 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2856 = true := by
  decide +kernel

theorem tot2856 : totK PA10K2 A10K2.t2856 = [0, 0, 661732299353, 2073671747873, 1713538408398, 395598745495, 25734533292, 0, 0, 0] := by
  decide +kernel

theorem rows2857 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2857 = true := by
  decide +kernel

theorem tot2857 : totK PA10K2 A10K2.t2857 = [0, 199895226948, 1018773767396, 1946020142420, 1378893981549, 230155196775, 6034215561, 0, 0, 0] := by
  decide +kernel

theorem rows2858 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2858 = true := by
  decide +kernel

theorem tot2858 : totK PA10K2 A10K2.t2858 = [0, 443649105951, 1767800494220, 1977567487538, 580963157404, 32877822373, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2859 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2859 = true := by
  decide +kernel

theorem tot2859 : totK PA10K2 A10K2.t2859 = [0, 142611917850, 920238634676, 2040942368859, 1388623973400, 208883491496, 6239673734, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
