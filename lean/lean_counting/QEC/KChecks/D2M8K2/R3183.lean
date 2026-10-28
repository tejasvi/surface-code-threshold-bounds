import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows12732 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12732 = true := by
  decide +kernel

theorem tot12732 : totK PD2M8K2 D2M8K2.t12732 = [0, 176791382431, 455566126585, 263559590504, 26406709991, 0, 0, 0] := by
  decide +kernel

theorem rows12733 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12733 = true := by
  decide +kernel

theorem tot12733 : totK PD2M8K2 D2M8K2.t12733 = [0, 177833708595, 463396225169, 241607698123, 15248009960, 0, 0, 0] := by
  decide +kernel

theorem rows12734 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12734 = true := by
  decide +kernel

theorem tot12734 : totK PD2M8K2 D2M8K2.t12734 = [0, 0, 253523702574, 506543542022, 130059636120, 0, 0, 0] := by
  decide +kernel

theorem rows12735 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12735 = true := by
  decide +kernel

theorem tot12735 : totK PD2M8K2 D2M8K2.t12735 = [0, 0, 176841197627, 460949738388, 219069024958, 9478845344, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
