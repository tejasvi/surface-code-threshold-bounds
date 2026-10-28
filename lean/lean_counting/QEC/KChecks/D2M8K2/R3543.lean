import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows14172 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14172 = true := by
  decide +kernel

theorem tot14172 : totK PD2M8K2 D2M8K2.t14172 = [0, 182748149967, 438635862899, 273796173011, 34168072533, 0, 0, 0] := by
  decide +kernel

theorem rows14173 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14173 = true := by
  decide +kernel

theorem tot14173 : totK PD2M8K2 D2M8K2.t14173 = [0, 169937826428, 467335453006, 249192583695, 12740861401, 0, 0, 0] := by
  decide +kernel

theorem rows14174 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14174 = true := by
  decide +kernel

theorem tot14174 : totK PD2M8K2 D2M8K2.t14174 = [0, 88825966916, 386636850426, 361359648523, 73557002115, 10444649207, 0, 0] := by
  decide +kernel

theorem rows14175 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14175 = true := by
  decide +kernel

theorem tot14175 : totK PD2M8K2 D2M8K2.t14175 = [0, 0, 170494325612, 456608205899, 248651690455, 16460032206, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
