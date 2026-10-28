import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2724 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2724 = true := by
  decide +kernel

theorem tot2724 : totK PA10K2 A10K2.t2724 = [0, 0, 605097007150, 2025182522112, 1704999415798, 364957828177, 25734533292, 0, 0, 0] := by
  decide +kernel

theorem rows2725 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2725 = true := by
  decide +kernel

theorem tot2725 : totK PA10K2 A10K2.t2725 = [0, 374286759930, 1313332004190, 1740226798488, 1086667385373, 196577165750, 6034215561, 0, 0, 0] := by
  decide +kernel

theorem rows2726 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2726 = true := by
  decide +kernel

theorem tot2726 : totK PA10K2 A10K2.t2726 = [0, 474263259421, 1898471751208, 1926379316870, 478569489502, 26521581199, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2727 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2727 = true := by
  decide +kernel

theorem tot2727 : totK PA10K2 A10K2.t2727 = [0, 0, 883976091943, 2394445488405, 1301956619246, 113943173993, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
