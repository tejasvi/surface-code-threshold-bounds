import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3984 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3984 = true := by
  decide +kernel

theorem tot3984 : totK PA10K2 A10K2.t3984 = [0, 0, 0, 780335918353, 2180140912408, 1480194439533, 218291868678, 6354482628, 0, 0] := by
  decide +kernel

theorem rows3985 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3985 = true := by
  decide +kernel

theorem tot3985 : totK PA10K2 A10K2.t3985 = [0, 0, 0, 457725415596, 1906315613471, 1959999960508, 453495563449, 26116334861, 0, 0] := by
  decide +kernel

theorem rows3986 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3986 = true := by
  decide +kernel

theorem tot3986 : totK PA10K2 A10K2.t3986 = [0, 0, 0, 640477614711, 2003497277176, 1824767060547, 429901642477, 18533161629, 0, 0] := by
  decide +kernel

theorem rows3987 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3987 = true := by
  decide +kernel

theorem tot3987 : totK PA10K2 A10K2.t3987 = [0, 0, 0, 317520726226, 1616291463762, 2114739759236, 584140393662, 31889781550, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
