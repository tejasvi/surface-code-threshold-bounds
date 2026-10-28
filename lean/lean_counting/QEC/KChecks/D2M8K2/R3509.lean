import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows14036 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14036 = true := by
  decide +kernel

theorem tot14036 : totK PD2M8K2 D2M8K2.t14036 = [0, 0, 301574371655, 490633980877, 101739971733, 1178750802, 0, 0] := by
  decide +kernel

theorem rows14037 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14037 = true := by
  decide +kernel

theorem tot14037 : totK PD2M8K2 D2M8K2.t14037 = [0, 0, 194245644558, 466447609134, 197552163846, 12017349186, 0, 0] := by
  decide +kernel

theorem rows14038 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14038 = true := by
  decide +kernel

theorem tot14038 : totK PD2M8K2 D2M8K2.t14038 = [0, 151715084213, 428083703085, 300188463122, 35367270523, 0, 0, 0] := by
  decide +kernel

theorem rows14039 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14039 = true := by
  decide +kernel

theorem tot14039 : totK PD2M8K2 D2M8K2.t14039 = [0, 211392754055, 458645000795, 213372161561, 15742371236, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
