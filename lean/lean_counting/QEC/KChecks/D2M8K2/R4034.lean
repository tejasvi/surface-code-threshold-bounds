import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows16136 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16136 = true := by
  decide +kernel

theorem tot16136 : totK PD2M8K2 D2M8K2.t16136 = [0, 71311081112, 240755810120, 393141067053, 182781715309, 8209931632, 0, 0] := by
  decide +kernel

theorem rows16137 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16137 = true := by
  decide +kernel

theorem tot16137 : totK PD2M8K2 D2M8K2.t16137 = [0, 189905983833, 465876288496, 253226678389, 23064966596, 0, 0, 0] := by
  decide +kernel

theorem rows16138 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16138 = true := by
  decide +kernel

theorem tot16138 : totK PD2M8K2 D2M8K2.t16138 = [0, 178627885223, 478151688660, 228713442603, 12373752831, 0, 0, 0] := by
  decide +kernel

theorem rows16139 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16139 = true := by
  decide +kernel

theorem tot16139 : totK PD2M8K2 D2M8K2.t16139 = [0, 0, 280492417575, 512703192725, 108713525302, 1164319620, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
