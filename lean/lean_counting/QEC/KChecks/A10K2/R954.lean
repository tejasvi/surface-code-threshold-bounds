import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3816 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3816 = true := by
  decide +kernel

theorem tot3816 : totK PA10K2 A10K2.t3816 = [0, 0, 0, 477890983485, 1891149301361, 1884698762592, 382200517683, 25667075836, 0, 0] := by
  decide +kernel

theorem rows3817 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3817 = true := by
  decide +kernel

theorem tot3817 : totK PA10K2 A10K2.t3817 = [0, 0, 0, 563795042069, 1914917151847, 1862373404989, 428511131951, 31265925590, 0, 0] := by
  decide +kernel

theorem rows3818 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3818 = true := by
  decide +kernel

theorem tot3818 : totK PA10K2 A10K2.t3818 = [0, 0, 0, 398432494548, 1753512909079, 2033321287169, 538262780922, 32744407728, 0, 0] := by
  decide +kernel

theorem rows3819 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3819 = true := by
  decide +kernel

theorem tot3819 : totK PA10K2 A10K2.t3819 = [0, 0, 0, 221888409560, 1135401039492, 2002401572818, 1077905738375, 165462991421, 5546304973, 0] := by
  decide +kernel

end QECKChecks.A10K2
