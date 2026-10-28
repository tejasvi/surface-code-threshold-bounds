import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4336 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4336 = true := by
  decide +kernel

theorem tot4336 : totK PA10K2 A10K2.t4336 = [0, 0, 0, 0, 695232914112, 2015215632306, 1561542102966, 379008486577, 25239774317, 0] := by
  decide +kernel

theorem rows4337 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4337 = true := by
  decide +kernel

theorem tot4337 : totK PA10K2 A10K2.t4337 = [0, 0, 0, 287930791013, 1240546013717, 1841405127617, 1051083615974, 179642457696, 5365973533, 0] := by
  decide +kernel

theorem rows4338 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4338 = true := by
  decide +kernel

theorem tot4338 : totK PA10K2 A10K2.t4338 = [0, 0, 0, 428342536580, 1711185559452, 1793744634296, 444292236934, 15977054524, 0, 0] := by
  decide +kernel

theorem rows4339 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4339 = true := by
  decide +kernel

theorem tot4339 : totK PA10K2 A10K2.t4339 = [0, 0, 0, 113147589240, 874328595306, 1982020632904, 1231750739493, 194755816594, 5528811039, 0] := by
  decide +kernel

end QECKChecks.A10K2
