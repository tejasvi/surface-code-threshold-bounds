import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2824 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2824 = true := by
  decide +kernel

theorem tot2824 : totK PA10K2 A10K2.t2824 = [0, 135666749101, 921802371747, 2008897562984, 1405702866424, 229912573556, 5517381808, 0, 0, 0] := by
  decide +kernel

theorem rows2825 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2825 = true := by
  decide +kernel

theorem tot2825 : totK PA10K2 A10K2.t2825 = [0, 492916436156, 1890865772532, 1890576831808, 485381071655, 26521581199, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2826 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2826 = true := by
  decide +kernel

theorem tot2826 : totK PA10K2 A10K2.t2826 = [0, 35691523517, 746514420927, 2145729652170, 1458783849759, 213926338260, 6121173289, 0, 0, 0] := by
  decide +kernel

theorem rows2827 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2827 = true := by
  decide +kernel

theorem tot2827 : totK PA10K2 A10K2.t2827 = [0, 521870137468, 1912692358419, 1995754244416, 570361830015, 32743093257, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
