import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows11320 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11320 = true := by
  decide +kernel

theorem tot11320 : totK PD2M8K2 D2M8K2.t11320 = [0, 179118419696, 479820685351, 229622743551, 12149367983, 0, 0, 0] := by
  decide +kernel

theorem rows11321 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11321 = true := by
  decide +kernel

theorem tot11321 : totK PD2M8K2 D2M8K2.t11321 = [0, 0, 316973248021, 468583590258, 77929513647, 1053411165, 0, 0] := by
  decide +kernel

theorem rows11322 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11322 = true := by
  decide +kernel

theorem tot11322 : totK PD2M8K2 D2M8K2.t11322 = [0, 118976915037, 337340186736, 324714146183, 81772134595, 3667207281, 0, 0] := by
  decide +kernel

theorem rows11323 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11323 = true := by
  decide +kernel

theorem tot11323 : totK PD2M8K2 D2M8K2.t11323 = [0, 176366899950, 455961618823, 262757511195, 23385096921, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
