import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2892 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2892 = true := by
  decide +kernel

theorem tot2892 : totK PA10K2 A10K2.t2892 = [177435414779, 1122131959409, 2148896468991, 1358618603696, 243028681109, 6853348008, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2893 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2893 = true := by
  decide +kernel

theorem tot2893 : totK PA10K2 A10K2.t2893 = [0, 538854696659, 1995123811177, 2132403728136, 505060590503, 12853939499, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2894 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2894 = true := by
  decide +kernel

theorem tot2894 : totK PA10K2 A10K2.t2894 = [0, 480414392987, 1690889638886, 1852817842363, 683162304740, 68939555567, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2895 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2895 = true := by
  decide +kernel

theorem tot2895 : totK PA10K2 A10K2.t2895 = [0, 297007965898, 1548110066775, 2215258874844, 823631080607, 60544467592, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
