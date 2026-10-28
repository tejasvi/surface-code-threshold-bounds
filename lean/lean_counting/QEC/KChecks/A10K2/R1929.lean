import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7716 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7716 = true := by
  decide +kernel

theorem tot7716 : totK PA10K2 A10K2.t7716 = [0, 0, 0, 511486637352, 1871348330594, 1885000501466, 447474137058, 17013015050, 0, 0] := by
  decide +kernel

theorem rows7717 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7717 = true := by
  decide +kernel

theorem tot7717 : totK PA10K2 A10K2.t7717 = [0, 0, 0, 461403095397, 1820612865060, 1929409260926, 475488771112, 32470938769, 0, 0] := by
  decide +kernel

theorem rows7718 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7718 = true := by
  decide +kernel

theorem tot7718 : totK PA10K2 A10K2.t7718 = [0, 0, 0, 637393340540, 2123602623961, 1732945118455, 282513701446, 6354609102, 0, 0] := by
  decide +kernel

theorem rows7719 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7719 = true := by
  decide +kernel

theorem tot7719 : totK PA10K2 A10K2.t7719 = [0, 0, 0, 533878049243, 1718785869741, 1806779587685, 510290043017, 36266333350, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
