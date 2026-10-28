import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2616 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2616 = true := by
  decide +kernel

theorem tot2616 : totK PA10K2 A10K2.t2616 = [0, 294356378534, 1207817627274, 1853181249439, 1116791408662, 177287303861, 5460492893, 0, 0, 0] := by
  decide +kernel

theorem rows2617 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2617 = true := by
  decide +kernel

theorem tot2617 : totK PA10K2 A10K2.t2617 = [0, 454642566388, 1778666339204, 1995338633296, 572880024382, 32846095359, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2618 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2618 = true := by
  decide +kernel

theorem tot2618 : totK PA10K2 A10K2.t2618 = [0, 0, 656615377711, 2119703734299, 1576866906996, 317738394950, 24969229125, 0, 0, 0] := by
  decide +kernel

theorem rows2619 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2619 = true := by
  decide +kernel

theorem tot2619 : totK PA10K2 A10K2.t2619 = [0, 342241960375, 1231551260955, 1788700809576, 1115758979803, 195821153372, 6034215561, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
