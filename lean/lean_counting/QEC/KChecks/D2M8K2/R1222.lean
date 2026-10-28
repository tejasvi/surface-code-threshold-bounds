import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4888 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4888 = true := by
  decide +kernel

theorem tot4888 : totK PD2M8K2 D2M8K2.t4888 = [0, 0, 154242224949, 379644620748, 234449812142, 94116792615, 9043051330, 0] := by
  decide +kernel

theorem rows4889 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4889 = true := by
  decide +kernel

theorem tot4889 : totK PD2M8K2 D2M8K2.t4889 = [0, 0, 198986901350, 469962817653, 214662260824, 12534051746, 0, 0] := by
  decide +kernel

theorem rows4890 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4890 = true := by
  decide +kernel

theorem tot4890 : totK PD2M8K2 D2M8K2.t4890 = [0, 0, 17557681974, 296435459173, 471003940814, 85304631343, 1310517177, 0] := by
  decide +kernel

theorem rows4891 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4891 = true := by
  decide +kernel

theorem tot4891 : totK PD2M8K2 D2M8K2.t4891 = [0, 0, 121982544061, 412713361406, 350031753933, 40856530956, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
