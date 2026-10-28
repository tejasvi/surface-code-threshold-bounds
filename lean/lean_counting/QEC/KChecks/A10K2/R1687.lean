import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6748 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6748 = true := by
  decide +kernel

theorem tot6748 : totK PA10K2 A10K2.t6748 = [0, 269885564472, 1368840054841, 2175070779085, 1130009444611, 120829578807, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6749 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6749 = true := by
  decide +kernel

theorem tot6749 : totK PA10K2 A10K2.t6749 = [0, 252824012363, 1240754982707, 1979744694097, 1202001780491, 213260217500, 7047025452, 0, 0, 0] := by
  decide +kernel

theorem rows6750 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6750 = true := by
  decide +kernel

theorem tot6750 : totK PA10K2 A10K2.t6750 = [0, 583435650787, 1896769281939, 1916221508845, 557874982461, 23581264317, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6751 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6751 = true := by
  decide +kernel

theorem tot6751 : totK PA10K2 A10K2.t6751 = [0, 31680252160, 876257515891, 2223942348594, 1577336328410, 256471742039, 6066958478, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
