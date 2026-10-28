import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5020 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5020 = true := by
  decide +kernel

theorem tot5020 : totK PD2M8K2 D2M8K2.t5020 = [0, 0, 174985200530, 460503629964, 228653425166, 16927042322, 0, 0] := by
  decide +kernel

theorem rows5021 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5021 = true := by
  decide +kernel

theorem tot5021 : totK PD2M8K2 D2M8K2.t5021 = [0, 0, 181942926901, 472508584402, 205734876969, 9653832318, 0, 0] := by
  decide +kernel

theorem rows5022 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5022 = true := by
  decide +kernel

theorem tot5022 : totK PD2M8K2 D2M8K2.t5022 = [0, 0, 106104768822, 407617157260, 303930185167, 40658672454, 1206465782, 0] := by
  decide +kernel

theorem rows5023 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5023 = true := by
  decide +kernel

theorem tot5023 : totK PD2M8K2 D2M8K2.t5023 = [0, 0, 38598824603, 323545567746, 448006394263, 57244853594, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
