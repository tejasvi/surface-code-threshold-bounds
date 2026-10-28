import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6028 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6028 = true := by
  decide +kernel

theorem tot6028 : totK PA10K2 A10K2.t6028 = [287457250577, 1258523911190, 1887251222742, 1128185628265, 195103454496, 5460492893, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6029 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6029 = true := by
  decide +kernel

theorem tot6029 : totK PA10K2 A10K2.t6029 = [233045995781, 1347174867135, 2143942366604, 899053877468, 65725581519, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6030 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6030 = true := by
  decide +kernel

theorem tot6030 : totK PA10K2 A10K2.t6030 = [293915060262, 1224625646259, 1873026332434, 1069540289139, 203458713903, 6354482628, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6031 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6031 = true := by
  decide +kernel

theorem tot6031 : totK PA10K2 A10K2.t6031 = [526633995392, 1940171075594, 2120664934436, 624847392983, 27769006694, 0, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
