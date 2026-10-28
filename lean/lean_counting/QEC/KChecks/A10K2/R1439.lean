import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5756 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5756 = true := by
  decide +kernel

theorem tot5756 : totK PA10K2 A10K2.t5756 = [0, 0, 378991267087, 1346661321776, 1805365259374, 1035859121718, 200246557625, 6354482628, 0, 0] := by
  decide +kernel

theorem rows5757 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5757 = true := by
  decide +kernel

theorem tot5757 : totK PA10K2 A10K2.t5757 = [0, 0, 181459769048, 1043873369792, 2174766699620, 1378958449608, 178501328839, 6962742351, 0, 0] := by
  decide +kernel

theorem rows5758 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5758 = true := by
  decide +kernel

theorem tot5758 : totK PA10K2 A10K2.t5758 = [0, 0, 463622061231, 1883803623951, 1908328998742, 454364803068, 25686058060, 0, 0, 0] := by
  decide +kernel

theorem rows5759 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5759 = true := by
  decide +kernel

theorem tot5759 : totK PA10K2 A10K2.t5759 = [0, 0, 164636681257, 959245629944, 1883101612071, 1265391272463, 282989820147, 24614390653, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
