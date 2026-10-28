import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3012 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3012 = true := by
  decide +kernel

theorem tot3012 : totK PA10K2 A10K2.t3012 = [0, 0, 0, 370445857423, 1662737663362, 2088258465545, 713227331047, 53844901745, 0, 0] := by
  decide +kernel

theorem rows3013 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3013 = true := by
  decide +kernel

theorem tot3013 : totK PA10K2 A10K2.t3013 = [0, 0, 0, 479678660173, 1838730082348, 1871763926170, 518046206912, 34193440607, 0, 0] := by
  decide +kernel

theorem rows3014 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3014 = true := by
  decide +kernel

theorem tot3014 : totK PA10K2 A10K2.t3014 = [0, 0, 0, 0, 772440756215, 2173040720906, 1483175903573, 260028579309, 7237400819, 0] := by
  decide +kernel

theorem rows3015 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3015 = true := by
  decide +kernel

theorem tot3015 : totK PA10K2 A10K2.t3015 = [0, 0, 0, 553529002408, 1925262850390, 1788055372585, 401374385320, 26845136505, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
