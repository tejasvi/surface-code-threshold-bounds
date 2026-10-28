import QECCountComp.KData.A6K2

namespace QECKChecks.A6K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem irow0 : rowCheckK PA6K2 tA6K2 ((nat_lit 2275), (nat_lit 10863738889), (nat_lit 0)) = true := by
  decide +kernel

theorem irow1 : rowCheckK PA6K2 tA6K2 ((nat_lit 6178), (nat_lit 9399746397), (nat_lit 0)) = true := by
  decide +kernel

theorem irow2 : rowCheckK PA6K2 tA6K2 ((nat_lit 3770), (nat_lit 15177985847), (nat_lit 0)) = true := by
  decide +kernel

theorem irow3 : rowCheckK PA6K2 tA6K2 ((nat_lit 10496), (nat_lit 15171530017), (nat_lit 0)) = true := by
  decide +kernel

theorem irow4 : rowCheckK PA6K2 tA6K2 ((nat_lit 14378), (nat_lit 9378831097), (nat_lit 0)) = true := by
  decide +kernel

theorem irow5 : rowCheckK PA6K2 tA6K2 ((nat_lit 11995), (nat_lit 7990454993), (nat_lit 0)) = true := by
  decide +kernel

theorem irow6 : rowCheckK PA6K2 tA6K2 ((nat_lit 9373), (nat_lit 6766917719), (nat_lit 0)) = true := by
  decide +kernel

theorem irow7 : rowCheckK PA6K2 tA6K2 ((nat_lit 17821), (nat_lit 5634698734), (nat_lit 0)) = true := by
  decide +kernel

theorem irow8 : rowCheckK PA6K2 tA6K2 ((nat_lit 22640), (nat_lit 15078107739), (nat_lit 0)) = true := by
  decide +kernel

theorem irow9 : rowCheckK PA6K2 tA6K2 ((nat_lit 19209), (nat_lit 9852997180), (nat_lit 0)) = true := by
  decide +kernel

theorem irow10 : rowCheckK PA6K2 tA6K2 ((nat_lit 27656), (nat_lit 14850925602), (nat_lit 0)) = true := by
  decide +kernel

theorem irow11 : rowCheckK PA6K2 tA6K2 ((nat_lit 30422), (nat_lit 14487558083), (nat_lit 0)) = true := by
  decide +kernel

theorem irow12 : rowCheckK PA6K2 tA6K2 ((nat_lit 28790), (nat_lit 16470726546), (nat_lit 0)) = true := by
  decide +kernel

theorem irow13 : rowCheckK PA6K2 tA6K2 ((nat_lit 25136), (nat_lit 15078107739), (nat_lit 0)) = true := by
  decide +kernel

theorem irow14 : rowCheckK PA6K2 tA6K2 ((nat_lit 16393), (nat_lit 10390662215), (nat_lit 0)) = true := by
  decide +kernel

end QECKChecks.A6K2
