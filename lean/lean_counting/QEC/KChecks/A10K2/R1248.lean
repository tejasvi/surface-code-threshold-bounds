import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4992 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4992 = true := by
  decide +kernel

theorem tot4992 : totK PA10K2 A10K2.t4992 = [113616355882, 563209962659, 1613560367941, 1907681733497, 704854695515, 64208876967, 0, 0, 0, 0] := by
  decide +kernel

theorem rows4993 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4993 = true := by
  decide +kernel

theorem tot4993 : totK PA10K2 A10K2.t4993 = [464427794452, 1832436734691, 1943273878668, 479692998199, 25686058060, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem rows4994 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4994 = true := by
  decide +kernel

theorem tot4994 : totK PA10K2 A10K2.t4994 = [164636681257, 919926570528, 1890884823967, 1373364654311, 345167090287, 25371180993, 0, 0, 0, 0] := by
  decide +kernel

theorem rows4995 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4995 = true := by
  decide +kernel

theorem tot4995 : totK PA10K2 A10K2.t4995 = [294549363032, 1108078229785, 1832306871119, 1304037994264, 224563145765, 5460492893, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
