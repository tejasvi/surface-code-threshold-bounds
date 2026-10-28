import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6500 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6500 = true := by
  decide +kernel

theorem tot6500 : totK PA10K2 A10K2.t6500 = [0, 0, 709064135625, 2082745011338, 1522716156679, 267655048974, 6354482628, 0, 0, 0] := by
  decide +kernel

theorem rows6501 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6501 = true := by
  decide +kernel

theorem tot6501 : totK PA10K2 A10K2.t6501 = [0, 0, 471213704242, 1781925869684, 1933639750897, 549836980710, 32470938769, 0, 0, 0] := by
  decide +kernel

theorem rows6502 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6502 = true := by
  decide +kernel

theorem tot6502 : totK PA10K2 A10K2.t6502 = [0, 0, 496526282785, 1935146702641, 2010163928123, 447769741114, 13227942247, 0, 0, 0] := by
  decide +kernel

theorem rows6503 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6503 = true := by
  decide +kernel

theorem tot6503 : totK PA10K2 A10K2.t6503 = [0, 0, 568013831436, 1868866772116, 1774858058037, 447997621296, 30953568651, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
