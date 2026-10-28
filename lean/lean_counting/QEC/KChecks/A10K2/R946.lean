import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3784 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3784 = true := by
  decide +kernel

theorem tot3784 : totK PA10K2 A10K2.t3784 = [0, 0, 0, 285441611041, 1538776509235, 2140526410543, 654727153751, 38902754494, 0, 0] := by
  decide +kernel

theorem rows3785 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3785 = true := by
  decide +kernel

theorem tot3785 : totK PA10K2 A10K2.t3785 = [0, 0, 0, 215763881691, 1091531866676, 2030766048299, 1255997625183, 188795561032, 6121173289, 0] := by
  decide +kernel

theorem rows3786 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3786 = true := by
  decide +kernel

theorem tot3786 : totK PA10K2 A10K2.t3786 = [0, 0, 0, 477180583076, 1892251437094, 2069735008003, 580724868053, 32712955001, 0, 0] := by
  decide +kernel

theorem rows3787 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3787 = true := by
  decide +kernel

theorem tot3787 : totK PA10K2 A10K2.t3787 = [0, 0, 516552094339, 1841316040011, 1687213356813, 467087752046, 165484496866, 24019724025, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
