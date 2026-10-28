import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3024 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3024 = true := by
  decide +kernel

theorem tot3024 : totK PA10K2 A10K2.t3024 = [0, 0, 0, 585927630277, 2038108522058, 1935520826178, 417988572723, 13231026584, 0, 0] := by
  decide +kernel

theorem rows3025 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3025 = true := by
  decide +kernel

theorem tot3025 : totK PA10K2 A10K2.t3025 = [0, 320479959089, 972451722066, 946123679463, 985895570107, 1228304732794, 518279520850, 49137536365, 0, 0] := by
  decide +kernel

theorem rows3026 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3026 = true := by
  decide +kernel

theorem tot3026 : totK PA10K2 A10K2.t3026 = [0, 541416715838, 1893693353139, 1898791878761, 476881221397, 17643329925, 0, 0, 0, 0] := by
  decide +kernel

theorem rows3027 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3027 = true := by
  decide +kernel

theorem tot3027 : totK PA10K2 A10K2.t3027 = [0, 0, 682138706946, 2068039263900, 1710442813117, 404063531063, 25734533292, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
