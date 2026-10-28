import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows9572 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9572 = true := by
  decide +kernel

theorem tot9572 : totK PD2M8K2 D2M8K2.t9572 = [0, 84745114217, 314703265571, 377642583749, 93541801259, 3667207281, 0, 0] := by
  decide +kernel

theorem rows9573 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9573 = true := by
  decide +kernel

theorem tot9573 : totK PD2M8K2 D2M8K2.t9573 = [0, 159950037561, 450993476043, 267456435721, 21958861232, 0, 0, 0] := by
  decide +kernel

theorem rows9574 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9574 = true := by
  decide +kernel

theorem tot9574 : totK PD2M8K2 D2M8K2.t9574 = [0, 181688270574, 471086925672, 246840757657, 15079379989, 0, 0, 0] := by
  decide +kernel

theorem rows9575 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9575 = true := by
  decide +kernel

theorem tot9575 : totK PD2M8K2 D2M8K2.t9575 = [174434339562, 426373226813, 214233948807, 61905415995, 9758758476, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
