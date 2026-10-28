import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows692 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t692 = true := by
  decide +kernel

theorem tot692 : totK PA10K2 A10K2.t692 = [0, 0, 844267922710, 2343397968276, 1369064872527, 134625777487, 0, 0, 0, 0] := by
  decide +kernel

theorem rows693 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t693 = true := by
  decide +kernel

theorem tot693 : totK PA10K2 A10K2.t693 = [0, 0, 480087321253, 1772628192684, 1891011833858, 501721218486, 31987755669, 0, 0, 0] := by
  decide +kernel

theorem rows694 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t694 = true := by
  decide +kernel

theorem tot694 : totK PA10K2 A10K2.t694 = [0, 0, 529976821767, 1958104569903, 1870249044103, 378459963050, 12718857877, 0, 0, 0] := by
  decide +kernel

theorem rows695 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t695 = true := by
  decide +kernel

theorem tot695 : totK PA10K2 A10K2.t695 = [0, 0, 414552127861, 1707057352795, 1983928210463, 543556133486, 32470943963, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
