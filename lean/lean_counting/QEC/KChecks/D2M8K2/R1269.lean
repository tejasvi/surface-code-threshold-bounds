import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5076 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5076 = true := by
  decide +kernel

theorem tot5076 : totK PD2M8K2 D2M8K2.t5076 = [0, 107013832152, 428112920994, 347495306377, 42537630182, 0, 0, 0] := by
  decide +kernel

theorem rows5077 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5077 = true := by
  decide +kernel

theorem tot5077 : totK PD2M8K2 D2M8K2.t5077 = [0, 0, 173750717273, 441169134572, 255939901271, 25356464804, 0, 0] := by
  decide +kernel

theorem rows5078 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5078 = true := by
  decide +kernel

theorem tot5078 : totK PD2M8K2 D2M8K2.t5078 = [0, 0, 158477363460, 484118494898, 253791223113, 7803142361, 0, 0] := by
  decide +kernel

theorem rows5079 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5079 = true := by
  decide +kernel

theorem tot5079 : totK PD2M8K2 D2M8K2.t5079 = [0, 178101252088, 439152684592, 243428842912, 30088152224, 4399788625, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
