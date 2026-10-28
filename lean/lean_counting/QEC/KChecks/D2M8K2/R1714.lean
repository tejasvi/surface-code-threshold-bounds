import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6856 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6856 = true := by
  decide +kernel

theorem tot6856 : totK PD2M8K2 D2M8K2.t6856 = [0, 168148840712, 454062044492, 262597855892, 17623538916, 0, 0, 0] := by
  decide +kernel

theorem rows6857 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6857 = true := by
  decide +kernel

theorem tot6857 : totK PD2M8K2 D2M8K2.t6857 = [0, 85003784765, 344058457269, 366736813916, 78946450201, 1171084559, 0, 0] := by
  decide +kernel

theorem rows6858 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6858 = true := by
  decide +kernel

theorem tot6858 : totK PD2M8K2 D2M8K2.t6858 = [0, 0, 205500557588, 471765060183, 177472823855, 10425178834, 0, 0] := by
  decide +kernel

theorem rows6859 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6859 = true := by
  decide +kernel

theorem tot6859 : totK PD2M8K2 D2M8K2.t6859 = [0, 172179909266, 460028984671, 245160305159, 27686849567, 1509187004, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
