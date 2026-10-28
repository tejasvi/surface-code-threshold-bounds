import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows8072 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t8072 = true := by
  decide +kernel

theorem tot8072 : totK PA10K2 A10K2.t8072 = [0, 0, 0, 685459774022, 2067202446732, 1763112210644, 409933744822, 18710738642, 0, 0] := by
  decide +kernel

theorem rows8073 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t8073 = true := by
  decide +kernel

theorem tot8073 : totK PA10K2 A10K2.t8073 = [0, 0, 253046812372, 1219594705834, 2039930413660, 1193220474470, 163634517058, 0, 0, 0] := by
  decide +kernel

theorem rows8074 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t8074 = true := by
  decide +kernel

theorem tot8074 : totK PA10K2 A10K2.t8074 = [0, 0, 615603840132, 2039088907212, 1901388411539, 468395556903, 23744887683, 0, 0, 0] := by
  decide +kernel

theorem rows8075 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t8075 = true := by
  decide +kernel

theorem tot8075 : totK PA10K2 A10K2.t8075 = [0, 0, 0, 740047504430, 2205232929051, 1702858471208, 294425025607, 6853348008, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
