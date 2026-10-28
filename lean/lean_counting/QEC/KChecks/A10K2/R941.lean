import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3764 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3764 = true := by
  decide +kernel

theorem tot3764 : totK PA10K2 A10K2.t3764 = [0, 0, 511776002785, 1724474467531, 1706210624070, 624796678911, 123282941067, 6034215561, 0, 0] := by
  decide +kernel

theorem rows3765 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3765 = true := by
  decide +kernel

theorem tot3765 : totK PA10K2 A10K2.t3765 = [0, 0, 304053839609, 1512886311879, 2089550010145, 765053431885, 50033367339, 0, 0, 0] := by
  decide +kernel

theorem rows3766 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3766 = true := by
  decide +kernel

theorem tot3766 : totK PA10K2 A10K2.t3766 = [0, 0, 0, 692177312561, 2085981901515, 1576989906348, 262936632263, 6354482628, 0, 0] := by
  decide +kernel

theorem rows3767 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3767 = true := by
  decide +kernel

theorem tot3767 : totK PA10K2 A10K2.t3767 = [0, 0, 0, 465874399384, 1815349759184, 1955705786135, 472014947631, 31987876949, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
