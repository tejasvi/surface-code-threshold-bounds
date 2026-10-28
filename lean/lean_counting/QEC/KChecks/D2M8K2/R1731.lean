import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6924 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6924 = true := by
  decide +kernel

theorem tot6924 : totK PD2M8K2 D2M8K2.t6924 = [0, 0, 165558101238, 473397543001, 220887532242, 8923894879, 0, 0] := by
  decide +kernel

theorem rows6925 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6925 = true := by
  decide +kernel

theorem tot6925 : totK PD2M8K2 D2M8K2.t6925 = [0, 0, 219031220651, 485246032632, 183690876851, 7718403079, 0, 0] := by
  decide +kernel

theorem rows6926 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6926 = true := by
  decide +kernel

theorem tot6926 : totK PD2M8K2 D2M8K2.t6926 = [0, 0, 158814820125, 472749522259, 226178332261, 8966096369, 0, 0] := by
  decide +kernel

theorem rows6927 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6927 = true := by
  decide +kernel

theorem tot6927 : totK PD2M8K2 D2M8K2.t6927 = [0, 0, 205273712191, 485070452424, 174272691089, 7472928540, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
