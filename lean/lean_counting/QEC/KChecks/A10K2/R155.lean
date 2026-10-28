import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows620 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t620 = true := by
  decide +kernel

theorem tot620 : totK PA10K2 A10K2.t620 = [0, 310152219116, 755818480026, 780156282912, 1421919129300, 1116901270476, 233528391130, 6354482628, 0, 0] := by
  decide +kernel

theorem rows621 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t621 = true := by
  decide +kernel

theorem tot621 : totK PA10K2 A10K2.t621 = [0, 498328713856, 1890721556742, 2032068307682, 534632123208, 31611289403, 0, 0, 0, 0] := by
  decide +kernel

theorem rows622 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t622 = true := by
  decide +kernel

theorem tot622 : totK PA10K2 A10K2.t622 = [0, 0, 723774878611, 2166055990243, 1675155348900, 382092495873, 25351274858, 0, 0, 0] := by
  decide +kernel

theorem rows623 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t623 = true := by
  decide +kernel

theorem tot623 : totK PA10K2 A10K2.t623 = [0, 287452481429, 1268472774588, 2002472816187, 1210790930854, 208605120291, 5459593153, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
