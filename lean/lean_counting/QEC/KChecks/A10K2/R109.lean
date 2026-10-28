import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows436 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t436 = true := by
  decide +kernel

theorem tot436 : totK PA10K2 A10K2.t436 = [0, 580293892768, 1927083669895, 1757287355450, 451883579974, 97734224745, 26011840508, 0, 0, 0] := by
  decide +kernel

theorem rows437 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t437 = true := by
  decide +kernel

theorem tot437 : totK PA10K2 A10K2.t437 = [0, 274878282901, 1429815244321, 2176608419756, 925680618383, 72953422289, 0, 0, 0, 0] := by
  decide +kernel

theorem rows438 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t438 = true := by
  decide +kernel

theorem tot438 : totK PA10K2 A10K2.t438 = [0, 0, 503418107181, 1862053210537, 1812348048710, 483248983145, 30831673886, 0, 0, 0] := by
  decide +kernel

theorem rows439 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t439 = true := by
  decide +kernel

theorem tot439 : totK PA10K2 A10K2.t439 = [0, 456211902719, 1708767216027, 1893059860049, 683596570700, 60517959978, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
