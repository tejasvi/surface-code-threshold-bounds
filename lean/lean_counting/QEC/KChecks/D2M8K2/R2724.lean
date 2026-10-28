import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows10896 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10896 = true := by
  decide +kernel

theorem tot10896 : totK PD2M8K2 D2M8K2.t10896 = [0, 0, 80405182910, 329843630578, 356346903227, 90143143518, 3472187823, 0] := by
  decide +kernel

theorem rows10897 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10897 = true := by
  decide +kernel

theorem tot10897 : totK PD2M8K2 D2M8K2.t10897 = [0, 0, 173862373540, 474906097258, 255346967283, 18418208341, 0, 0] := by
  decide +kernel

theorem rows10898 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10898 = true := by
  decide +kernel

theorem tot10898 : totK PD2M8K2 D2M8K2.t10898 = [0, 0, 87678414668, 371647535532, 352747292045, 58426220464, 1053411165, 0] := by
  decide +kernel

theorem rows10899 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10899 = true := by
  decide +kernel

theorem tot10899 : totK PD2M8K2 D2M8K2.t10899 = [0, 0, 84745114217, 318011627198, 369800389843, 91514123584, 3667207281, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
