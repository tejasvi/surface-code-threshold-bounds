import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4224 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4224 = true := by
  decide +kernel

theorem tot4224 : totK PA10K2 A10K2.t4224 = [548282633765, 1874341275846, 1735536961003, 426618711188, 25686058060, 93840089069, 84918787380, 6354482628, 0, 0] := by
  decide +kernel

theorem rows4225 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4225 = true := by
  decide +kernel

theorem tot4225 : totK PA10K2 A10K2.t4225 = [294540101292, 1415060938314, 2165080070850, 965241203545, 82306616445, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem rows4226 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4226 = true := by
  decide +kernel

theorem tot4226 : totK PA10K2 A10K2.t4226 = [0, 501826089983, 1868256438376, 1848032806892, 484171875586, 30831673886, 0, 0, 0, 0] := by
  decide +kernel

theorem rows4227 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4227 = true := by
  decide +kernel

theorem tot4227 : totK PA10K2 A10K2.t4227 = [559707398140, 1743176431053, 1830777029955, 681480988584, 70193027768, 0, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
